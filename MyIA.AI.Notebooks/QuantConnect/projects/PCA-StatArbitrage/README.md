# PCA-StatArbitrage

**Classe d'actifs :** Actions US (top 100 par volume en dollars)
**ID projet Cloud :** `33281920` (`1630-baseline-PCAStatArbitrage`, IBKR + aligné 2018-2025 ; `main.py` = canonique + paramétrage des dates uniquement)

## Description

Arbitrage statistique par PCA compatible QC Cloud utilisant la PCA de sklearn au lieu de numpy/scipy. Ajuste les composantes principales sur le panneau des log-prix d'un univers top 100 actions US, régresse chaque titre sur les facteurs PCA, et trade les z-scores résiduels comme signal contrarien de retour à la moyenne (long sur la queue z<-1.5, pondérations proportionnelles à la déviation du z, rotation mensuelle complète via `set_holdings(liquidate=True)`).

**Consolidé depuis PCA-StatArb** (version statsmodels, non compatible QC Cloud) et **ML-PCA-StatArb** (code identique avec commentaires supplémentaires).

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/PCA-StatArbitrage"`
**QC Cloud :** Déployé (voir ID projet Cloud ci-dessus). Le `main.py` commité ici est la copie canonique avec `set_brokerage_model(IBKR, MARGIN)` (frais réels) ; les dates 2015-2024 codées en dur sont celles par défaut de l'auteur.

## Métriques de backtest

| Métrique | Valeur | Fenêtre / frais |
|----------|--------|-----------------|
| Méthode | sklearn PCA + OLS résiduel mean-reversion | — |
| Rééquilibrage | Mensuel (rotation complète, `set_holdings liquidate=True`) | — |
| Univers | Top 100 actions US par volume en dollars | — |
| Sharpe | **0.205** | 2018-2025, IBKR frais réels (#1630-aligné) |
| CAGR | 6.76 % | 2018-2025, IBKR |
| MaxDD | 31.8 % | 2018-2025, IBKR |
| PSR | 1.4 % (niveau bruit) | 2018-2025, IBKR |
| Sharpe (précédent) | 0.399 | 2015-2024, IBKR (fenêtre auteur) |
| Sharpe (contrôle sans frais) | 0.205 (byte-identical) | 2018-2025, sans brokerage |

**Caveat #1630 (vérifié 2026-06-23).** Le 0.40 du catalogue ne survit pas à l'alignement #1630 : 0.399 -> **0.205** (-49 %, PSR 1.4 % = bruit). Deux constats : **(a) la chute est un effet de FENÊTRE, pas de frais** — le 0.399 du README était déjà un chiffre IBKR, donc la dégradation vient de la montée en momentum Mag7 2024-25 de la fenêtre alignée, structurellement hostile à la mean-reversion PCA contrarienne (les noms résiduels oversold continuent de tomber, les gagnants continuent de gagner) ; **(b) la stratégie est IMMUNE aux frais** — un clone sans brokerage codé en dur de la logique identique (backtest `63fce57d`) retourne un 0.205 byte-identical, donc retirer le brokerage ne change rien à 3 décimales près. Ceci réfute la prédiction pré-run « rotation mensuelle complète => vulnérable aux frais » et étend la classe regime-3 near-immune du discriminateur #1630 (l'homogénéité des frais du panier actions US domine sur le turnover par événement ; cf EMA-Cross-Stocks IBKR 0.991 = no-brokerage 0.991). Analyse complète : `docs/qc/qc-comparative-backtests.md` finding #40 (See #1630).

## Fichiers

- `main.py` — Stratégie (sklearn PCA + OLS mean-reversion, consolidé depuis PCA-StatArb + ML-PCA-StatArb, brokerage IBKR).

## Références

- Avellaneda, M. & Lee, J.-H. (2010), *Statistical Arbitrage in the US Equities Market*. (Framework de mean-reversion résiduelle PCA.)
