# ML-EnhancedPairs

**Asset class:** US Equities (pairs)
**Cloud project ID:** 37318734

## Description

Stratégie de pairs trading avec sélection de paires configurable et filtrage du signal par RandomForest. Dans `main.py`, la liste fixe de paires sectorielles est le comportement par défaut ; un mode optionnel remplace cette liste par des candidates formées après regroupement PCA/OPTICS. Le RandomForest intervient ensuite dans le pipeline de signal, après les filtres de cointégration et de demi-vie.

## Modes de sélection des paires (livre, chap. 06-09, #18961)

- **`useClusterPairs=false` (défaut)** : conserve la liste fixe de cinq paires d'ETF sectoriels ; c'est le comportement par défaut de `main.py`.
- **`useClusterPairs=true`** : au premier jour de bourse de chaque mois (`MonthStart("SPY")`), l'algorithme standardise trois ans de rendements quotidiens, les réduit à trois composantes principales (`PCA(n_components=3)`), puis regroupe les expositions de facteur avec `OPTICS`. Il forme les paires candidates **au sein de chaque cluster** ; les points de bruit OPTICS (étiquette -1) ne sont associés à aucune paire. Les filtres de cointégration (Engle-Granger/ADF), de demi-vie et le RandomForest s'appliquent ensuite aux paires candidates.

Ce mode de `main.py` porte l'étape 1-2 du notebook de référence du livre `06 Applied Machine Learning/09 ML Trading Pairs Selection/research.ipynb` (HandsOnAITradingBook, commit `e025f21`) : regroupement avant cointégration. Le livre applique la méthode à l'univers IWB (~1000 actifs) ; ce projet la met à l'épreuve sur les 7 ETF sectoriels du dépôt. Le carnet [`quantbook.ipynb`](quantbook.ipynb) est une analyse de recherche distincte : il ne contient pas de PCA, d'OPTICS ni de regroupement. Il construit des combinaisons de paires parmi SPY, QQQ, IWM, EFA et AGG lorsque leurs historiques sont disponibles, puis applique cointégration, variables de spread et RandomForest.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-EnhancedPairs"`
**QC Cloud:** Deployed as project 37318734. Backtests avec paramètre `useClusterPairs` (`true`/`false`, défaut `false`).

## Métriques des backtests

Le tableau ci-dessous compare deux backtests QC Cloud du projet Lean (`main.py`), et non les résultats du `quantbook.ipynb`. Période commune : 2015-01-01 → 2024-12-31, IBKR MARGIN, capital initial de 100 000 $ et même univers :

| Mesure | `main.py` — paires fixes | `main.py` — clusters PCA + OPTICS |
| -------- | ------------------------ | ------------------------ |
| Ratio de Sharpe | -2.486 | -1.415 |
| Rendement annuel composé | -0.361% | -0.857% |
| Baisse maximale | 4.900% | 12.700% |
| Nombre d'ordres | 158 | 540 |

Backtests QC Cloud (`18961-baseline-fixed-pairs` et `18961-cluster-pca-optics`, projet 37318734), exécutés avec les deux valeurs du paramètre `useClusterPairs` de `main.py`. Le QuantBook utilise une autre période et une autre sélection d'actifs : ses calculs ne sont pas représentés par ce tableau.

**Lecture honnête (verdict : NO BEATS).** Sur cet univers de 7 ETFs, le mode cluster améliore le Sharpe (-2.486 → -1.415) mais dégrade le reste : rendement annuel plus faible (-0.361 % → -0.857 %), drawdown plus profond (4.9 % → 12.7 %), 3,4x plus d'ordres (158 → 540) et 3,2x plus de frais ($920 -> $2 984, résultat net -3.55 % -> -8.25 %). Le portage démontre la **mécanique** du ch. 06-09 (regroupement avant cointégration ; l'écart de comportement est massif et mesurable : turnover 1.58 % -> 6.01 %), pas un gain — cohérent avec l'échelle : le livre applique la méthode à ~1000 actifs IWB où le regroupement élimine l'essentiel des fausses paires ; sur 7 ETFs voisins, OPTICS fragmente l'univers sans écarter les rapprochements sectoriels trompeurs.

## QuantBook de recherche et limites

Le [carnet `quantbook.ipynb`](quantbook.ipynb) est un prototype de recherche fondé sur des données QuantConnect. Son code déclare au QuantBook les dates 2020-01-01 à 2025-12-31, puis demande cinq ans d'historique via `qb.History(..., 365*5, ...)`. Dans un QuantBook neuf, cette requête est ancrée à `qb.Time` (initialisé à `StartDate`) : la fenêtre effectivement chargée est 2012-09-28–2019-12-31. Les analyses du carnet portent sur cette fenêtre, pas sur 2020–2025 ni sur la période des backtests Cloud du tableau.

Le carnet construit des paires candidates à partir des ETF disponibles SPY, QQQ, IWM, EFA et AGG, teste leur cointégration, calcule des variables de spread (Z-score, demi-vie, volatilité et momentum) et entraîne un RandomForest avec une étiquette d'entrée définie par |Z-score| > 2. Il n'implémente pas le mode de sélection par clusters : cette capacité réside dans `main.py` et s'active avec `useClusterPairs=true`. Le carnet ajuste son RandomForest sur les exemples de l'ensemble de la fenêtre avant de parcourir cette même fenêtre dans sa simulation ; ce parcours n'est donc pas une validation chronologique hors échantillon. La simulation ne déduit pas non plus de frais de transaction. Les résultats et seuils indiqués comme références ou champs « à remplir » dans le carnet ne sont pas les métriques du tableau Cloud.

Le carnet signale que sa fenêtre historique exclut notamment la période COVID et le drawdown de 2022. Son analyse exploratoire ne démontre pas une performance pour 2020–2025.

## Files

- [`main.py`](main.py) - stratégie Lean : paires fixes par défaut, mode optionnel PCA/OPTICS via `GetParameter("useClusterPairs")`
- [`quantbook.ipynb`](quantbook.ipynb) - QuantBook de recherche : cointégration et RandomForest sur des paires candidates, sans clustering PCA/OPTICS
