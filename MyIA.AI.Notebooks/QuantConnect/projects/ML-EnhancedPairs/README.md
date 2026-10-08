# ML-EnhancedPairs

**Asset class:** US Equities (pairs)
**Cloud project ID:** 37318734

## Description

ML-enhanced pairs trading. Uses ML to improve pair selection and signal generation beyond traditional cointegration tests.

## Pair-selection modes (book ch. 06-09, #18961)

- **`useClusterPairs=false` (défaut)** : la liste fixe de 5 paires sector ETFs, comportement historique inchangé.
- **`useClusterPairs=true`** : chaque mois (premier jour de bourse, `MonthStart("SPY")`), l'algorithme standardise 3 ans de rendements quotidiens de l'univers, les réduit à 3 composantes principales (`PCA(n_components=3)`), regroupe les expositions de facteur par `OPTICS`, puis tire les paires candidates **à l'intérieur de chaque cluster** (le bruit OPTICS, label -1, ne rejoint aucune paire). Le pipeline aval (Engle-Granger/ADF, half-life, RandomForest) s'applique ensuite à ces paires comme aux fixes.

C'est le portage de l'étape 1-2 du notebook de référence `06 Applied Machine Learning/09 ML Trading Pairs Selection/research.ipynb` (HandsOnAITradingBook, commit `e025f21`) : regroupement AVANT cointégration. Le livre applique la méthode à l'univers IWB (~1000 actifs) ; ce projet la démontre sur les 7 sector ETFs du dépôt — assez pour séparer quelques groupes et mesurer l'effet, pas assez pour en faire un usage de production.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-EnhancedPairs"`
**QC Cloud:** Deployed as project 37318734. Backtests avec paramètre `useClusterPairs` (`true`/`false`, défaut `false`).

## Backtest Metrics

Période commune 2015-01-01 → 2024-12-31, IBKR MARGIN, cash 100 000 $, même univers :

| Metric | Baseline (paires fixes) | Cluster (PCA + OPTICS) |
| -------- | ------------------------ | ------------------------ |
| Sharpe Ratio | -2.486 | -1.415 |
| Compounding Annual Return | -0.361% | -0.857% |
| Max Drawdown | 4.900% | 12.700% |
| Total Orders | 158 | 540 |

Backtests réels QC Cloud (`18961-baseline-fixed-pairs` et `18961-cluster-pca-optics`, projet 37318734, mode sélectionné par le paramètre `useClusterPairs`).

**Lecture honnête (verdict : NO BEATS).** Sur cet univers de 7 ETFs, le mode cluster améliore le Sharpe (-2.486 → -1.415) mais dégrade le reste : rendement annuel plus faible (-0.361 % → -0.857 %), drawdown plus profond (4.9 % → 12.7 %), 3,4x plus d'ordres (158 → 540) et 3,2x plus de frais ($920 -> $2 984, résultat net -3.55 % -> -8.25 %). Le portage démontre la **mécanique** du ch. 06-09 (regroupement avant cointégration ; l'écart de comportement est massif et mesurable : turnover 1.58 % -> 6.01 %), pas un gain — cohérent avec l'échelle : le livre applique la méthode à ~1000 actifs IWB où le regroupement élimine l'essentiel des fausses paires ; sur 7 ETFs voisins, OPTICS fragmente l'univers sans écarter les rapprochements sectoriels trompeurs.

## Files

- main.py - Strategy (mode cluster derrière `GetParameter("useClusterPairs")`)
- quantbook.ipynb - QuantBook de recherche : analyse de la stratégie de pairs trading améliorée (mode cluster, données natives QC)
