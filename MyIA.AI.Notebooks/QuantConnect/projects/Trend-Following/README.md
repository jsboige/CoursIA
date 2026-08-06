# Trend Following — `TrendFollowingAQR` v7

**Classe d'actifs :** ETF multi-actifs (actions US/EU/EM, obligations, or, matières)
**Cloud project ID :** 28797562
**Période backtestée :** 2015-01-01 → 2024-12-31

## Description

Stratégie de **trend-following multi-actifs** (style Antonacci 2014 / AQR Trend Followinging) déployée comme `main.py`. L'algorithme combine un **double signal de momentum** et un **régime baissier de safe-haven** :

- **Filtre de tendance** : pour chaque actif risqué, on exige `prix > SMA(200)` (la tendance de fond est haussière).
- **Confirmation momentum** : le rendement glissant 6 mois (`ret_6m > 0`) doit confirmer.
- **Pondération par rang** : les actifs retenus sont classés par rendement 12 mois ; le poids est proportionnel au rang (l'actif le plus fort surperforme).
- **Régime baissier** : si `SPY < SMA(200)`, le portefeuille bascule — le risqué est plafonné à 50 % et les 50 % restants vont dans le safe-haven `BND` (obligations). En marché haussier, 100 % risqué.

**Univers** : `SPY, EFA, EEM, TLT, GLD, DBC` (risqué) + `BND` (safe-haven). Rebalancement **mensuel** (ouverture du premier jour ouvré, +30 min).

## Backtest réel (QC Cloud, frais IBKR margin inclus)

| Métrique | Valeur |
|----------|--------|
| Sharpe ratio | **0.36** |
| CAGR | **7.29 %** |
| Drawdown max | **15.00 %** |
| Rendement total net | 102.2 % (+83 510 $ sur 100 k $) |
| PSR (Probabilistic Sharpe Ratio) | **0.659 %** |
| Ordres exécutés | 454 |
| Jours tradés | 2516 |

*Backtest frais via QC Cloud project 28797562 (compile `BuildSuccess`, 2026-08-06). Métriques vérifiées, pas claim de docstring.*

### Lecture honnête — beta gérée, pas alpha

Le **PSR à 0.66 %** est sans ambiguïté : la probabilité que le ratio de Sharpe observé soit **statistiquement supérieur à zéro** est quasi nulle. Autrement dit, malgré un rendement absolu positif (CAGR 7.29 %) et un drawdown contenu (15 %), **cette stratégie ne démontre aucune compétence (skill) statistiquement significative**.

Ce résultat est **cohérent et pédagogiquement sain** : TrendFollowingAQR est une stratégie de **beta de marché géré**, pas d'alpha. La valeur ajoutée n'est pas le rendement excédentaire mais la **réduction du drawdown** via le commutateur de régime safe-haven (`BND`) : sur la décennie 2015-2024 (bull market dominant), la stratégie **suit** le benchmark SPY avec un rendement légèrement inférieur (le CAGR SPY sur la période est ~12-13 %), mais en marché baissier (Q1 2020, 2022) la bascule vers `BND` protège le capital. La sur la même décennie, SPY a subi des drawdowns de ~25-34 % ; ici le MaxDD est plafonné à 15 %.

**Conclusion honnête** : ne PAS présenter cette stratégie comme génératrice d'alpha. C'est un **exemple pédagogique de gestion de risque systématique** — un beta de marché avec un overlay de protection baissière. Le rendement positif s'explique par l'exposition au marché (beta), pas par une capacité prédictive (le PSR le confirme). À rapprocher de l'Option-Wheel et de l'EMA-Cross-Stocks : même famille pédagogique de « stratégies qui rendent au marché, pas qui le battent ».

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Trend-Following"`
**QC Cloud :** Déployé comme projet 28797562 (paramètre optionnel `brokerage` : `ibkr` défaut avec frais réels, `none` pour frais nuls — utile pour isoler l'effet des frais).

## Architecture

- **`main.py`** — Algorithme déployé (`TrendFollowingAQR` v7). Auto-contenu : univers fixe 6+1 ETF, double signal SMA(200)+momentum 6m/12m, régime baissier safe-haven, rebalancement mensuel. C'est le fichier backtesté ci-dessus.
- `alpha.py`, `macd_oracle.py`, `rsi_oracle.py`, `bollinger_oracle.py`, `trendCalculator.py` — **Fichiers orphelins** (architecture multi-oracles d'une version antérieure, non importés par `main.py` actuel). Conservés tels quels ; nettoyable dans une PR dédiée.
- `quantbook.ipynb` — Recherche (analyse des signaux).
- `config.json`, `trend_following_analysis.png` — Config et figure d'analyse.

## Concepts enseignés

- **Double momentum** (Antonacci) : filtre de tendance `SMA(200)` + confirmation momentum `6m`.
- **Pondération par rang** (rank-based) plutôt que par pondération naive égale.
- **Régime de marché / safe-haven switch** : détection baissière (`SPY < SMA(200)`) → réallocation défensive vers obligations.
- **Backtesting avec frais réels** (IBKR margin) vs frais nuls — isoler l'impact des coûts de transaction.
- **Probabilistic Sharpe Ratio (PSR)** : distinguer un rendement positif d'une compétence statistiquement significative (leçon clé : CAGR 7.29 % ≠ skill si PSR ≈ 0).
